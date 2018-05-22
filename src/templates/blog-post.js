import React from 'react'
import Helmet from 'react-helmet'
import Link from 'gatsby-link'
import get from 'lodash/get'
import rehypeReact from "rehype-react";

import AnnotatedCode from '../components/AnnotatedCode'
import Bio from '../components/Bio'
// import { rhythm, scale } from '../utils/typography'

const renderAst = new rehypeReact({
  createElement: React.createElement,
  components: { "annotated-code": AnnotatedCode },
}).Compiler;

class BlogPostTemplate extends React.Component {
  render() {
    const post = this.props.data.markdownRemark
    const siteTitle = get(this.props, 'data.site.siteMetadata.title')
    const { previous, next } = this.props.pathContext

    return (
      <div>
        <Helmet title={`${post.frontmatter.title} | ${siteTitle}`} />
        <h1 style={{
          fontFamily: 'Nunino, sans-serif',
          fontWeight: 300,
        }}>
          {post.frontmatter.title}
        </h1>
        <p
          style={{
            // ...scale(-1 / 5),
            display: 'block',
            marginBottom: '50px',
            // marginBottom: rhythm(1),
            // marginTop: rhythm(-1),
          }}
        >
          {post.frontmatter.date}
        </p>
        {renderAst(post.htmlAst)}
        <hr
          style={{
            backgroundColor: '#0a2e6b',
            margin: '30px 0',
            height: '1px',
            border: 'none',
          }}
        />
        <Bio />

        <ul
          style={{
            display: 'flex',
            flexWrap: 'wrap',
            justifyContent: 'space-between',
            listStyle: 'none',
            padding: 0,
          }}
        >
          {previous && (
            <li>
              <Link to={previous.fields.slug} rel="prev">
                ← {previous.frontmatter.title}
              </Link>
            </li>
          )}

          {next && (
            <li>
              <Link to={next.fields.slug} rel="next">
                {next.frontmatter.title} →
              </Link>
            </li>
          )}
        </ul>
      </div>
    )
  }
}

export default BlogPostTemplate

export const pageQuery = graphql`
  query BlogPostBySlug($slug: String!) {
    site {
      siteMetadata {
        title
        author
      }
    }
    markdownRemark(fields: { slug: { eq: $slug } }) {
      id
      htmlAst
      frontmatter {
        title
        date(formatString: "MMMM DD, YYYY")
      }
    }
  }
`
